%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:46 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 112 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden('#skF_1'(A_17,B_18),B_18)
      | r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_90,plain,(
    ! [C_30,B_31,A_32] :
      ( r2_hidden(C_30,B_31)
      | ~ r2_hidden(C_30,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_155,plain,(
    ! [A_45,B_46,B_47] :
      ( r2_hidden('#skF_2'(A_45,B_46),B_47)
      | ~ r1_tarski(B_46,B_47)
      | r1_xboole_0(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_10,c_90])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_409,plain,(
    ! [A_98,B_99,B_100,B_101] :
      ( r2_hidden('#skF_2'(A_98,B_99),B_100)
      | ~ r1_tarski(B_101,B_100)
      | ~ r1_tarski(B_99,B_101)
      | r1_xboole_0(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_421,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_2'(A_98,B_99),k2_relat_1('#skF_4'))
      | ~ r1_tarski(B_99,'#skF_3')
      | r1_xboole_0(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_24,c_409])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_101,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(k2_relat_1(B_34),A_35)
      | k10_relat_1(B_34,A_35) != k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_287,plain,(
    ! [C_70,A_71,B_72] :
      ( ~ r2_hidden(C_70,A_71)
      | ~ r2_hidden(C_70,k2_relat_1(B_72))
      | k10_relat_1(B_72,A_71) != k1_xboole_0
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_439,plain,(
    ! [A_104,B_105,B_106] :
      ( ~ r2_hidden('#skF_2'(A_104,B_105),k2_relat_1(B_106))
      | k10_relat_1(B_106,A_104) != k1_xboole_0
      | ~ v1_relat_1(B_106)
      | r1_xboole_0(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_12,c_287])).

tff(c_442,plain,(
    ! [A_98,B_99] :
      ( k10_relat_1('#skF_4',A_98) != k1_xboole_0
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_99,'#skF_3')
      | r1_xboole_0(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_421,c_439])).

tff(c_486,plain,(
    ! [A_109,B_110] :
      ( k10_relat_1('#skF_4',A_109) != k1_xboole_0
      | ~ r1_tarski(B_110,'#skF_3')
      | r1_xboole_0(A_109,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_442])).

tff(c_16,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_500,plain,(
    ! [B_111] :
      ( k1_xboole_0 = B_111
      | k10_relat_1('#skF_4',B_111) != k1_xboole_0
      | ~ r1_tarski(B_111,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_486,c_16])).

tff(c_508,plain,
    ( k1_xboole_0 = '#skF_3'
    | k10_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_500])).

tff(c_515,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_508])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n008.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:37:30 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.17/1.31  
% 2.17/1.31  %Foreground sorts:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Background operators:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Foreground operators:
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.17/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.31  
% 2.17/1.32  tff(f_79, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.17/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.17/1.32  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.17/1.32  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.17/1.32  tff(f_62, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.17/1.32  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.32  tff(c_22, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.32  tff(c_40, plain, (![A_17, B_18]: (~r2_hidden('#skF_1'(A_17, B_18), B_18) | r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.32  tff(c_45, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_40])).
% 2.17/1.32  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.32  tff(c_24, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.32  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.32  tff(c_90, plain, (![C_30, B_31, A_32]: (r2_hidden(C_30, B_31) | ~r2_hidden(C_30, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.32  tff(c_155, plain, (![A_45, B_46, B_47]: (r2_hidden('#skF_2'(A_45, B_46), B_47) | ~r1_tarski(B_46, B_47) | r1_xboole_0(A_45, B_46))), inference(resolution, [status(thm)], [c_10, c_90])).
% 2.17/1.32  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.32  tff(c_409, plain, (![A_98, B_99, B_100, B_101]: (r2_hidden('#skF_2'(A_98, B_99), B_100) | ~r1_tarski(B_101, B_100) | ~r1_tarski(B_99, B_101) | r1_xboole_0(A_98, B_99))), inference(resolution, [status(thm)], [c_155, c_2])).
% 2.17/1.32  tff(c_421, plain, (![A_98, B_99]: (r2_hidden('#skF_2'(A_98, B_99), k2_relat_1('#skF_4')) | ~r1_tarski(B_99, '#skF_3') | r1_xboole_0(A_98, B_99))), inference(resolution, [status(thm)], [c_24, c_409])).
% 2.17/1.32  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.32  tff(c_101, plain, (![B_34, A_35]: (r1_xboole_0(k2_relat_1(B_34), A_35) | k10_relat_1(B_34, A_35)!=k1_xboole_0 | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.17/1.32  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.32  tff(c_287, plain, (![C_70, A_71, B_72]: (~r2_hidden(C_70, A_71) | ~r2_hidden(C_70, k2_relat_1(B_72)) | k10_relat_1(B_72, A_71)!=k1_xboole_0 | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_101, c_8])).
% 2.17/1.32  tff(c_439, plain, (![A_104, B_105, B_106]: (~r2_hidden('#skF_2'(A_104, B_105), k2_relat_1(B_106)) | k10_relat_1(B_106, A_104)!=k1_xboole_0 | ~v1_relat_1(B_106) | r1_xboole_0(A_104, B_105))), inference(resolution, [status(thm)], [c_12, c_287])).
% 2.17/1.32  tff(c_442, plain, (![A_98, B_99]: (k10_relat_1('#skF_4', A_98)!=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_tarski(B_99, '#skF_3') | r1_xboole_0(A_98, B_99))), inference(resolution, [status(thm)], [c_421, c_439])).
% 2.17/1.32  tff(c_486, plain, (![A_109, B_110]: (k10_relat_1('#skF_4', A_109)!=k1_xboole_0 | ~r1_tarski(B_110, '#skF_3') | r1_xboole_0(A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_442])).
% 2.17/1.32  tff(c_16, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.32  tff(c_500, plain, (![B_111]: (k1_xboole_0=B_111 | k10_relat_1('#skF_4', B_111)!=k1_xboole_0 | ~r1_tarski(B_111, '#skF_3'))), inference(resolution, [status(thm)], [c_486, c_16])).
% 2.17/1.32  tff(c_508, plain, (k1_xboole_0='#skF_3' | k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_45, c_500])).
% 2.17/1.32  tff(c_515, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_508])).
% 2.17/1.32  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_515])).
% 2.17/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  Inference rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Ref     : 0
% 2.17/1.32  #Sup     : 114
% 2.17/1.32  #Fact    : 0
% 2.17/1.32  #Define  : 0
% 2.17/1.32  #Split   : 1
% 2.17/1.32  #Chain   : 0
% 2.17/1.32  #Close   : 0
% 2.17/1.32  
% 2.17/1.32  Ordering : KBO
% 2.17/1.32  
% 2.17/1.32  Simplification rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Subsume      : 35
% 2.17/1.32  #Demod        : 9
% 2.17/1.32  #Tautology    : 17
% 2.17/1.32  #SimpNegUnit  : 1
% 2.17/1.32  #BackRed      : 0
% 2.17/1.32  
% 2.17/1.32  #Partial instantiations: 0
% 2.17/1.32  #Strategies tried      : 1
% 2.17/1.32  
% 2.17/1.32  Timing (in seconds)
% 2.17/1.32  ----------------------
% 2.17/1.32  Preprocessing        : 0.28
% 2.17/1.32  Parsing              : 0.15
% 2.17/1.32  CNF conversion       : 0.02
% 2.17/1.32  Main loop            : 0.29
% 2.17/1.32  Inferencing          : 0.11
% 2.17/1.32  Reduction            : 0.07
% 2.17/1.33  Demodulation         : 0.05
% 2.17/1.33  BG Simplification    : 0.01
% 2.17/1.33  Subsumption          : 0.08
% 2.17/1.33  Abstraction          : 0.01
% 2.17/1.33  MUC search           : 0.00
% 2.17/1.33  Cooper               : 0.00
% 2.17/1.33  Total                : 0.60
% 2.17/1.33  Index Insertion      : 0.00
% 2.17/1.33  Index Deletion       : 0.00
% 2.17/1.33  Index Matching       : 0.00
% 2.17/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
