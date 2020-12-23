%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:20 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   61 (  65 expanded)
%              Number of leaves         :   37 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 (  86 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_65,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_48,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [C_54,A_55] :
      ( r1_tarski(C_54,A_55)
      | ~ r2_hidden(C_54,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_174,plain,(
    ! [A_55] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_55)),A_55)
      | v1_xboole_0(k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_177,plain,(
    ! [A_55] : r1_tarski('#skF_1'(k1_zfmisc_1(A_55)),A_55) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_174])).

tff(c_179,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(A_57,B_58) = B_58
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_184,plain,(
    ! [A_59] : k2_xboole_0('#skF_1'(k1_zfmisc_1(A_59)),A_59) = A_59 ),
    inference(resolution,[status(thm)],[c_177,c_179])).

tff(c_79,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_29,B_30] : k2_xboole_0(k1_tarski(A_29),B_30) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    ! [B_44,A_29] : k2_xboole_0(B_44,k1_tarski(A_29)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_42])).

tff(c_191,plain,(
    ! [A_29] : k1_tarski(A_29) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_95])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_419,plain,(
    ! [D_99,C_100,B_101,A_102] :
      ( r2_hidden(k1_funct_1(D_99,C_100),B_101)
      | k1_xboole_0 = B_101
      | ~ r2_hidden(C_100,A_102)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_2(D_99,A_102,B_101)
      | ~ v1_funct_1(D_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_455,plain,(
    ! [D_109,B_110] :
      ( r2_hidden(k1_funct_1(D_109,'#skF_8'),B_110)
      | k1_xboole_0 = B_110
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_110)))
      | ~ v1_funct_2(D_109,'#skF_6',B_110)
      | ~ v1_funct_1(D_109) ) ),
    inference(resolution,[status(thm)],[c_50,c_419])).

tff(c_458,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_455])).

tff(c_461,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_458])).

tff(c_462,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_461])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_467,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_462,c_10])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.43  
% 2.34/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.44  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 2.34/1.44  
% 2.34/1.44  %Foreground sorts:
% 2.34/1.44  
% 2.34/1.44  
% 2.34/1.44  %Background operators:
% 2.34/1.44  
% 2.34/1.44  
% 2.34/1.44  %Foreground operators:
% 2.34/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.34/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.34/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.34/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.34/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.34/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.44  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.34/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.34/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.44  
% 2.34/1.45  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.34/1.45  tff(f_65, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.34/1.45  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.34/1.45  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.34/1.45  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.34/1.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.34/1.45  tff(f_62, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.34/1.45  tff(f_77, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.34/1.45  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.34/1.45  tff(c_48, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.34/1.45  tff(c_44, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.34/1.45  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.45  tff(c_170, plain, (![C_54, A_55]: (r1_tarski(C_54, A_55) | ~r2_hidden(C_54, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.34/1.45  tff(c_174, plain, (![A_55]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_55)), A_55) | v1_xboole_0(k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_6, c_170])).
% 2.34/1.45  tff(c_177, plain, (![A_55]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_55)), A_55))), inference(negUnitSimplification, [status(thm)], [c_44, c_174])).
% 2.34/1.45  tff(c_179, plain, (![A_57, B_58]: (k2_xboole_0(A_57, B_58)=B_58 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.45  tff(c_184, plain, (![A_59]: (k2_xboole_0('#skF_1'(k1_zfmisc_1(A_59)), A_59)=A_59)), inference(resolution, [status(thm)], [c_177, c_179])).
% 2.34/1.45  tff(c_79, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.45  tff(c_42, plain, (![A_29, B_30]: (k2_xboole_0(k1_tarski(A_29), B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.45  tff(c_95, plain, (![B_44, A_29]: (k2_xboole_0(B_44, k1_tarski(A_29))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_42])).
% 2.34/1.45  tff(c_191, plain, (![A_29]: (k1_tarski(A_29)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184, c_95])).
% 2.34/1.45  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.34/1.45  tff(c_54, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.34/1.45  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.34/1.45  tff(c_50, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.34/1.45  tff(c_419, plain, (![D_99, C_100, B_101, A_102]: (r2_hidden(k1_funct_1(D_99, C_100), B_101) | k1_xboole_0=B_101 | ~r2_hidden(C_100, A_102) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_2(D_99, A_102, B_101) | ~v1_funct_1(D_99))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.34/1.45  tff(c_455, plain, (![D_109, B_110]: (r2_hidden(k1_funct_1(D_109, '#skF_8'), B_110) | k1_xboole_0=B_110 | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_110))) | ~v1_funct_2(D_109, '#skF_6', B_110) | ~v1_funct_1(D_109))), inference(resolution, [status(thm)], [c_50, c_419])).
% 2.34/1.45  tff(c_458, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_455])).
% 2.34/1.45  tff(c_461, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_458])).
% 2.34/1.45  tff(c_462, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_191, c_461])).
% 2.34/1.45  tff(c_10, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.45  tff(c_467, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_462, c_10])).
% 2.34/1.45  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_467])).
% 2.34/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.45  
% 2.34/1.45  Inference rules
% 2.34/1.45  ----------------------
% 2.34/1.45  #Ref     : 0
% 2.34/1.45  #Sup     : 89
% 2.34/1.45  #Fact    : 0
% 2.34/1.45  #Define  : 0
% 2.34/1.45  #Split   : 0
% 2.34/1.45  #Chain   : 0
% 2.34/1.45  #Close   : 0
% 2.34/1.45  
% 2.34/1.45  Ordering : KBO
% 2.34/1.45  
% 2.34/1.45  Simplification rules
% 2.34/1.45  ----------------------
% 2.34/1.45  #Subsume      : 10
% 2.34/1.45  #Demod        : 12
% 2.34/1.45  #Tautology    : 40
% 2.34/1.45  #SimpNegUnit  : 5
% 2.34/1.45  #BackRed      : 0
% 2.34/1.45  
% 2.34/1.45  #Partial instantiations: 0
% 2.34/1.45  #Strategies tried      : 1
% 2.34/1.45  
% 2.34/1.45  Timing (in seconds)
% 2.34/1.45  ----------------------
% 2.34/1.45  Preprocessing        : 0.36
% 2.34/1.45  Parsing              : 0.19
% 2.34/1.45  CNF conversion       : 0.03
% 2.34/1.45  Main loop            : 0.26
% 2.34/1.45  Inferencing          : 0.10
% 2.34/1.45  Reduction            : 0.08
% 2.34/1.45  Demodulation         : 0.05
% 2.34/1.45  BG Simplification    : 0.02
% 2.34/1.45  Subsumption          : 0.05
% 2.34/1.45  Abstraction          : 0.02
% 2.34/1.45  MUC search           : 0.00
% 2.34/1.45  Cooper               : 0.00
% 2.34/1.45  Total                : 0.65
% 2.34/1.45  Index Insertion      : 0.00
% 2.34/1.45  Index Deletion       : 0.00
% 2.34/1.45  Index Matching       : 0.00
% 2.34/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
