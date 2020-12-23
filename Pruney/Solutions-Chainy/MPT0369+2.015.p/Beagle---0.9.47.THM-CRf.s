%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:53 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   56 (  68 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 122 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_69,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_81,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_69])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,A_21)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_265,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k3_subset_1(A_70,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_279,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_265])).

tff(c_458,plain,(
    ! [D_86,A_87,B_88] :
      ( r2_hidden(D_86,k4_xboole_0(A_87,B_88))
      | r2_hidden(D_86,B_88)
      | ~ r2_hidden(D_86,A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_528,plain,(
    ! [D_90] :
      ( r2_hidden(D_90,k3_subset_1('#skF_5','#skF_6'))
      | r2_hidden(D_90,'#skF_6')
      | ~ r2_hidden(D_90,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_458])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_7',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_546,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_528,c_50])).

tff(c_559,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_546])).

tff(c_563,plain,
    ( ~ m1_subset_1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_559])).

tff(c_566,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_563])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_566])).

tff(c_570,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_588,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_2'(A_97,B_98),A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_601,plain,(
    ! [A_97,B_98] :
      ( ~ v1_xboole_0(A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_588,c_2])).

tff(c_38,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_610,plain,(
    ! [B_103,A_104] :
      ( B_103 = A_104
      | ~ r1_tarski(B_103,A_104)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_623,plain,(
    ! [A_105] :
      ( k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_610])).

tff(c_641,plain,(
    ! [A_106] :
      ( k1_xboole_0 = A_106
      | ~ v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_601,c_623])).

tff(c_644,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_570,c_641])).

tff(c_651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.41  
% 2.51/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.51/1.41  
% 2.51/1.41  %Foreground sorts:
% 2.51/1.41  
% 2.51/1.41  
% 2.51/1.41  %Background operators:
% 2.51/1.41  
% 2.51/1.41  
% 2.51/1.41  %Foreground operators:
% 2.51/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.51/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.51/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.51/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.51/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.41  
% 2.51/1.42  tff(f_90, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.51/1.42  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.51/1.42  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.51/1.42  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.51/1.42  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.51/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.51/1.42  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.51/1.42  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.42  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.42  tff(c_54, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.42  tff(c_69, plain, (![B_36, A_37]: (v1_xboole_0(B_36) | ~m1_subset_1(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.42  tff(c_81, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_69])).
% 2.51/1.42  tff(c_82, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_81])).
% 2.51/1.42  tff(c_42, plain, (![B_22, A_21]: (r2_hidden(B_22, A_21) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.42  tff(c_52, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.42  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.42  tff(c_265, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k3_subset_1(A_70, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.42  tff(c_279, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_265])).
% 2.51/1.42  tff(c_458, plain, (![D_86, A_87, B_88]: (r2_hidden(D_86, k4_xboole_0(A_87, B_88)) | r2_hidden(D_86, B_88) | ~r2_hidden(D_86, A_87))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.42  tff(c_528, plain, (![D_90]: (r2_hidden(D_90, k3_subset_1('#skF_5', '#skF_6')) | r2_hidden(D_90, '#skF_6') | ~r2_hidden(D_90, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_279, c_458])).
% 2.51/1.42  tff(c_50, plain, (~r2_hidden('#skF_7', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.42  tff(c_546, plain, (r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_528, c_50])).
% 2.51/1.42  tff(c_559, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_546])).
% 2.51/1.42  tff(c_563, plain, (~m1_subset_1('#skF_7', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_559])).
% 2.51/1.42  tff(c_566, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_563])).
% 2.51/1.42  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_566])).
% 2.51/1.42  tff(c_570, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_81])).
% 2.51/1.42  tff(c_588, plain, (![A_97, B_98]: (r2_hidden('#skF_2'(A_97, B_98), A_97) | r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.42  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.42  tff(c_601, plain, (![A_97, B_98]: (~v1_xboole_0(A_97) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_588, c_2])).
% 2.51/1.42  tff(c_38, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.42  tff(c_610, plain, (![B_103, A_104]: (B_103=A_104 | ~r1_tarski(B_103, A_104) | ~r1_tarski(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.42  tff(c_623, plain, (![A_105]: (k1_xboole_0=A_105 | ~r1_tarski(A_105, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_610])).
% 2.51/1.42  tff(c_641, plain, (![A_106]: (k1_xboole_0=A_106 | ~v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_601, c_623])).
% 2.51/1.42  tff(c_644, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_570, c_641])).
% 2.51/1.42  tff(c_651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_644])).
% 2.51/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.42  
% 2.51/1.42  Inference rules
% 2.51/1.42  ----------------------
% 2.51/1.42  #Ref     : 0
% 2.51/1.42  #Sup     : 120
% 2.51/1.42  #Fact    : 0
% 2.51/1.42  #Define  : 0
% 2.51/1.42  #Split   : 8
% 2.51/1.42  #Chain   : 0
% 2.51/1.42  #Close   : 0
% 2.51/1.42  
% 2.51/1.42  Ordering : KBO
% 2.51/1.42  
% 2.51/1.42  Simplification rules
% 2.51/1.42  ----------------------
% 2.51/1.42  #Subsume      : 20
% 2.51/1.42  #Demod        : 7
% 2.51/1.42  #Tautology    : 29
% 2.51/1.42  #SimpNegUnit  : 18
% 2.51/1.42  #BackRed      : 5
% 2.51/1.42  
% 2.51/1.42  #Partial instantiations: 0
% 2.51/1.42  #Strategies tried      : 1
% 2.51/1.42  
% 2.51/1.42  Timing (in seconds)
% 2.51/1.42  ----------------------
% 2.51/1.43  Preprocessing        : 0.32
% 2.51/1.43  Parsing              : 0.17
% 2.51/1.43  CNF conversion       : 0.02
% 2.51/1.43  Main loop            : 0.28
% 2.51/1.43  Inferencing          : 0.10
% 2.51/1.43  Reduction            : 0.08
% 2.51/1.43  Demodulation         : 0.05
% 2.51/1.43  BG Simplification    : 0.02
% 2.51/1.43  Subsumption          : 0.06
% 2.51/1.43  Abstraction          : 0.01
% 2.51/1.43  MUC search           : 0.00
% 2.51/1.43  Cooper               : 0.00
% 2.51/1.43  Total                : 0.63
% 2.51/1.43  Index Insertion      : 0.00
% 2.51/1.43  Index Deletion       : 0.00
% 2.51/1.43  Index Matching       : 0.00
% 2.51/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
