%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:18 EST 2020

% Result     : Theorem 8.68s
% Output     : CNFRefutation 8.68s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 134 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 281 expanded)
%              Number of equality atoms :    8 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_55,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_70,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_45,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_79,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_44,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_32,plain,(
    ! [A_14] : r2_hidden(A_14,k1_ordinal1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_73,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ r1_ordinal1(A_12,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_461,plain,(
    ! [B_76,A_77] :
      ( r2_hidden(B_76,A_77)
      | B_76 = A_77
      | r2_hidden(A_77,B_76)
      | ~ v3_ordinal1(B_76)
      | ~ v3_ordinal1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_tarski(A_11)) = k1_ordinal1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [D_36,A_37,B_38] :
      ( ~ r2_hidden(D_36,A_37)
      | r2_hidden(D_36,k2_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_157,plain,(
    ! [D_50,A_51] :
      ( ~ r2_hidden(D_50,A_51)
      | r2_hidden(D_50,k1_ordinal1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_80])).

tff(c_185,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_72])).

tff(c_503,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_461,c_185])).

tff(c_608,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_503])).

tff(c_638,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_644,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_638,c_38])).

tff(c_648,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_644])).

tff(c_652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_73,c_648])).

tff(c_653,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_657,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_72])).

tff(c_662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_657])).

tff(c_663,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_663])).

tff(c_666,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_36,plain,(
    ! [B_20,A_18] :
      ( r2_hidden(B_20,A_18)
      | r1_ordinal1(A_18,B_20)
      | ~ v3_ordinal1(B_20)
      | ~ v3_ordinal1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_667,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1021,plain,(
    ! [D_117,B_118,A_119] :
      ( r2_hidden(D_117,B_118)
      | r2_hidden(D_117,A_119)
      | ~ r2_hidden(D_117,k2_xboole_0(A_119,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2733,plain,(
    ! [D_233,A_234] :
      ( r2_hidden(D_233,k1_tarski(A_234))
      | r2_hidden(D_233,A_234)
      | ~ r2_hidden(D_233,k1_ordinal1(A_234)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1021])).

tff(c_11184,plain,(
    ! [A_666,D_667] :
      ( ~ r1_tarski(k1_tarski(A_666),D_667)
      | r2_hidden(D_667,A_666)
      | ~ r2_hidden(D_667,k1_ordinal1(A_666)) ) ),
    inference(resolution,[status(thm)],[c_2733,c_38])).

tff(c_11280,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_667,c_11184])).

tff(c_11282,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11280])).

tff(c_11292,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_11282])).

tff(c_11300,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_11292])).

tff(c_11306,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_11300])).

tff(c_11308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_666,c_11306])).

tff(c_11309,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_11280])).

tff(c_826,plain,(
    ! [B_103,A_104] :
      ( r2_hidden(B_103,A_104)
      | r1_ordinal1(A_104,B_103)
      | ~ v3_ordinal1(B_103)
      | ~ v3_ordinal1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_873,plain,(
    ! [A_104,B_103] :
      ( ~ r2_hidden(A_104,B_103)
      | r1_ordinal1(A_104,B_103)
      | ~ v3_ordinal1(B_103)
      | ~ v3_ordinal1(A_104) ) ),
    inference(resolution,[status(thm)],[c_826,c_2])).

tff(c_11313,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11309,c_873])).

tff(c_11321,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_11313])).

tff(c_11323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_666,c_11321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.68/3.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.68/3.24  
% 8.68/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.68/3.24  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 8.68/3.24  
% 8.68/3.24  %Foreground sorts:
% 8.68/3.24  
% 8.68/3.24  
% 8.68/3.24  %Background operators:
% 8.68/3.24  
% 8.68/3.24  
% 8.68/3.24  %Foreground operators:
% 8.68/3.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.68/3.24  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 8.68/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.68/3.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.68/3.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.68/3.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.68/3.24  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 8.68/3.24  tff('#skF_3', type, '#skF_3': $i).
% 8.68/3.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.68/3.24  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 8.68/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.68/3.24  tff('#skF_4', type, '#skF_4': $i).
% 8.68/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.68/3.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.68/3.24  
% 8.68/3.25  tff(f_94, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 8.68/3.25  tff(f_55, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 8.68/3.25  tff(f_53, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 8.68/3.25  tff(f_70, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 8.68/3.25  tff(f_45, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 8.68/3.25  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 8.68/3.25  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.68/3.25  tff(f_79, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 8.68/3.25  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.68/3.25  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 8.68/3.25  tff(c_44, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.68/3.25  tff(c_72, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 8.68/3.25  tff(c_32, plain, (![A_14]: (r2_hidden(A_14, k1_ordinal1(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.68/3.25  tff(c_42, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.68/3.25  tff(c_40, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.68/3.25  tff(c_50, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.68/3.25  tff(c_73, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 8.68/3.25  tff(c_30, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~r1_ordinal1(A_12, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.68/3.25  tff(c_461, plain, (![B_76, A_77]: (r2_hidden(B_76, A_77) | B_76=A_77 | r2_hidden(A_77, B_76) | ~v3_ordinal1(B_76) | ~v3_ordinal1(A_77))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.68/3.25  tff(c_26, plain, (![A_11]: (k2_xboole_0(A_11, k1_tarski(A_11))=k1_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.68/3.25  tff(c_80, plain, (![D_36, A_37, B_38]: (~r2_hidden(D_36, A_37) | r2_hidden(D_36, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.68/3.25  tff(c_157, plain, (![D_50, A_51]: (~r2_hidden(D_50, A_51) | r2_hidden(D_50, k1_ordinal1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_80])).
% 8.68/3.25  tff(c_185, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_157, c_72])).
% 8.68/3.25  tff(c_503, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_461, c_185])).
% 8.68/3.25  tff(c_608, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_503])).
% 8.68/3.25  tff(c_638, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_608])).
% 8.68/3.25  tff(c_38, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.68/3.25  tff(c_644, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_638, c_38])).
% 8.68/3.25  tff(c_648, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_644])).
% 8.68/3.25  tff(c_652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_73, c_648])).
% 8.68/3.25  tff(c_653, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_608])).
% 8.68/3.25  tff(c_657, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_72])).
% 8.68/3.25  tff(c_662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_657])).
% 8.68/3.25  tff(c_663, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 8.68/3.25  tff(c_665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_663])).
% 8.68/3.25  tff(c_666, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 8.68/3.25  tff(c_36, plain, (![B_20, A_18]: (r2_hidden(B_20, A_18) | r1_ordinal1(A_18, B_20) | ~v3_ordinal1(B_20) | ~v3_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.68/3.25  tff(c_24, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.68/3.25  tff(c_667, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 8.68/3.25  tff(c_1021, plain, (![D_117, B_118, A_119]: (r2_hidden(D_117, B_118) | r2_hidden(D_117, A_119) | ~r2_hidden(D_117, k2_xboole_0(A_119, B_118)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.68/3.25  tff(c_2733, plain, (![D_233, A_234]: (r2_hidden(D_233, k1_tarski(A_234)) | r2_hidden(D_233, A_234) | ~r2_hidden(D_233, k1_ordinal1(A_234)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1021])).
% 8.68/3.25  tff(c_11184, plain, (![A_666, D_667]: (~r1_tarski(k1_tarski(A_666), D_667) | r2_hidden(D_667, A_666) | ~r2_hidden(D_667, k1_ordinal1(A_666)))), inference(resolution, [status(thm)], [c_2733, c_38])).
% 8.68/3.25  tff(c_11280, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_667, c_11184])).
% 8.68/3.25  tff(c_11282, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_11280])).
% 8.68/3.25  tff(c_11292, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_11282])).
% 8.68/3.25  tff(c_11300, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_11292])).
% 8.68/3.25  tff(c_11306, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_11300])).
% 8.68/3.25  tff(c_11308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_666, c_11306])).
% 8.68/3.25  tff(c_11309, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_11280])).
% 8.68/3.25  tff(c_826, plain, (![B_103, A_104]: (r2_hidden(B_103, A_104) | r1_ordinal1(A_104, B_103) | ~v3_ordinal1(B_103) | ~v3_ordinal1(A_104))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.68/3.25  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.68/3.25  tff(c_873, plain, (![A_104, B_103]: (~r2_hidden(A_104, B_103) | r1_ordinal1(A_104, B_103) | ~v3_ordinal1(B_103) | ~v3_ordinal1(A_104))), inference(resolution, [status(thm)], [c_826, c_2])).
% 8.68/3.25  tff(c_11313, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_11309, c_873])).
% 8.68/3.25  tff(c_11321, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_11313])).
% 8.68/3.25  tff(c_11323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_666, c_11321])).
% 8.68/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.68/3.25  
% 8.68/3.25  Inference rules
% 8.68/3.25  ----------------------
% 8.68/3.25  #Ref     : 0
% 8.68/3.25  #Sup     : 2382
% 8.68/3.25  #Fact    : 12
% 8.68/3.25  #Define  : 0
% 8.68/3.25  #Split   : 6
% 8.68/3.25  #Chain   : 0
% 8.68/3.25  #Close   : 0
% 8.68/3.25  
% 8.68/3.25  Ordering : KBO
% 8.68/3.25  
% 8.68/3.25  Simplification rules
% 8.68/3.25  ----------------------
% 8.68/3.25  #Subsume      : 522
% 8.68/3.25  #Demod        : 80
% 8.68/3.25  #Tautology    : 70
% 8.68/3.25  #SimpNegUnit  : 35
% 8.68/3.25  #BackRed      : 7
% 8.68/3.25  
% 8.68/3.25  #Partial instantiations: 0
% 8.68/3.25  #Strategies tried      : 1
% 8.68/3.25  
% 8.68/3.25  Timing (in seconds)
% 8.68/3.25  ----------------------
% 8.68/3.25  Preprocessing        : 0.28
% 8.68/3.25  Parsing              : 0.15
% 8.68/3.25  CNF conversion       : 0.02
% 8.68/3.25  Main loop            : 2.18
% 8.68/3.25  Inferencing          : 0.51
% 8.68/3.25  Reduction            : 0.59
% 8.68/3.25  Demodulation         : 0.27
% 8.68/3.25  BG Simplification    : 0.08
% 8.68/3.25  Subsumption          : 0.83
% 8.68/3.25  Abstraction          : 0.09
% 8.68/3.25  MUC search           : 0.00
% 8.68/3.25  Cooper               : 0.00
% 8.68/3.25  Total                : 2.49
% 8.68/3.25  Index Insertion      : 0.00
% 8.68/3.25  Index Deletion       : 0.00
% 8.68/3.25  Index Matching       : 0.00
% 8.68/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
