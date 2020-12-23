%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:26 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 109 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_637,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r2_hidden('#skF_1'(A_87,B_88,C_89),B_88)
      | r2_hidden('#skF_2'(A_87,B_88,C_89),C_89)
      | k4_xboole_0(A_87,B_88) = C_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_644,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_637])).

tff(c_1414,plain,(
    ! [A_131,C_132] :
      ( r2_hidden('#skF_2'(A_131,A_131,C_132),C_132)
      | k4_xboole_0(A_131,A_131) = C_132 ) ),
    inference(resolution,[status(thm)],[c_18,c_637])).

tff(c_26,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_tarski(A_27,k4_xboole_0(B_29,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [C_30] : r1_xboole_0(k1_xboole_0,C_30) ),
    inference(resolution,[status(thm)],[c_26,c_52])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_62,plain,(
    ! [C_30] : k4_xboole_0(k1_xboole_0,C_30) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_30])).

tff(c_147,plain,(
    ! [D_44,B_45,A_46] :
      ( ~ r2_hidden(D_44,B_45)
      | ~ r2_hidden(D_44,k4_xboole_0(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [D_44,C_30] :
      ( ~ r2_hidden(D_44,C_30)
      | ~ r2_hidden(D_44,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_147])).

tff(c_1726,plain,(
    ! [A_146,C_147] :
      ( ~ r2_hidden('#skF_2'(A_146,A_146,C_147),k1_xboole_0)
      | k4_xboole_0(A_146,A_146) = C_147 ) ),
    inference(resolution,[status(thm)],[c_1414,c_153])).

tff(c_1744,plain,(
    ! [A_148] : k4_xboole_0(A_148,A_148) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_644,c_1726])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_267,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_271,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_267])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_309,plain,(
    ! [A_70] :
      ( r1_xboole_0(A_70,'#skF_5')
      | ~ r1_tarski(A_70,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_22])).

tff(c_317,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_309])).

tff(c_323,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_317,c_30])).

tff(c_34,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_xboole_0(A_17,k4_xboole_0(C_19,B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_346,plain,(
    ! [A_71] :
      ( r1_xboole_0(A_71,'#skF_4')
      | ~ r1_tarski(A_71,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_34])).

tff(c_426,plain,(
    ! [A_77] :
      ( k4_xboole_0(A_77,'#skF_4') = A_77
      | ~ r1_tarski(A_77,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_346,c_30])).

tff(c_436,plain,(
    k4_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_426])).

tff(c_1769,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1744,c_436])).

tff(c_1815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:09:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.58  
% 3.57/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.57/1.59  
% 3.57/1.59  %Foreground sorts:
% 3.57/1.59  
% 3.57/1.59  
% 3.57/1.59  %Background operators:
% 3.57/1.59  
% 3.57/1.59  
% 3.57/1.59  %Foreground operators:
% 3.57/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.57/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.57/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.57/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.57/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.57/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.59  
% 3.57/1.60  tff(f_68, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.57/1.60  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.57/1.60  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.57/1.60  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.57/1.60  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.57/1.60  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.57/1.60  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.57/1.60  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.57/1.60  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.60  tff(c_637, plain, (![A_87, B_88, C_89]: (~r2_hidden('#skF_1'(A_87, B_88, C_89), B_88) | r2_hidden('#skF_2'(A_87, B_88, C_89), C_89) | k4_xboole_0(A_87, B_88)=C_89)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.60  tff(c_644, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_637])).
% 3.57/1.60  tff(c_1414, plain, (![A_131, C_132]: (r2_hidden('#skF_2'(A_131, A_131, C_132), C_132) | k4_xboole_0(A_131, A_131)=C_132)), inference(resolution, [status(thm)], [c_18, c_637])).
% 3.57/1.60  tff(c_26, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.60  tff(c_52, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, C_28) | ~r1_tarski(A_27, k4_xboole_0(B_29, C_28)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.60  tff(c_58, plain, (![C_30]: (r1_xboole_0(k1_xboole_0, C_30))), inference(resolution, [status(thm)], [c_26, c_52])).
% 3.57/1.60  tff(c_30, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.57/1.60  tff(c_62, plain, (![C_30]: (k4_xboole_0(k1_xboole_0, C_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_30])).
% 3.57/1.60  tff(c_147, plain, (![D_44, B_45, A_46]: (~r2_hidden(D_44, B_45) | ~r2_hidden(D_44, k4_xboole_0(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.60  tff(c_153, plain, (![D_44, C_30]: (~r2_hidden(D_44, C_30) | ~r2_hidden(D_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_147])).
% 3.57/1.60  tff(c_1726, plain, (![A_146, C_147]: (~r2_hidden('#skF_2'(A_146, A_146, C_147), k1_xboole_0) | k4_xboole_0(A_146, A_146)=C_147)), inference(resolution, [status(thm)], [c_1414, c_153])).
% 3.57/1.60  tff(c_1744, plain, (![A_148]: (k4_xboole_0(A_148, A_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_644, c_1726])).
% 3.57/1.60  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.57/1.60  tff(c_40, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.57/1.60  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.57/1.60  tff(c_267, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.57/1.60  tff(c_271, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_267])).
% 3.57/1.60  tff(c_22, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_tarski(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.60  tff(c_309, plain, (![A_70]: (r1_xboole_0(A_70, '#skF_5') | ~r1_tarski(A_70, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_271, c_22])).
% 3.57/1.60  tff(c_317, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_309])).
% 3.57/1.60  tff(c_323, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_317, c_30])).
% 3.57/1.60  tff(c_34, plain, (![A_17, C_19, B_18]: (r1_xboole_0(A_17, k4_xboole_0(C_19, B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.57/1.60  tff(c_346, plain, (![A_71]: (r1_xboole_0(A_71, '#skF_4') | ~r1_tarski(A_71, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_323, c_34])).
% 3.57/1.60  tff(c_426, plain, (![A_77]: (k4_xboole_0(A_77, '#skF_4')=A_77 | ~r1_tarski(A_77, '#skF_5'))), inference(resolution, [status(thm)], [c_346, c_30])).
% 3.57/1.60  tff(c_436, plain, (k4_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_42, c_426])).
% 3.57/1.60  tff(c_1769, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1744, c_436])).
% 3.57/1.60  tff(c_1815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1769])).
% 3.57/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.60  
% 3.57/1.60  Inference rules
% 3.57/1.60  ----------------------
% 3.57/1.60  #Ref     : 0
% 3.57/1.60  #Sup     : 442
% 3.57/1.60  #Fact    : 0
% 3.57/1.60  #Define  : 0
% 3.57/1.60  #Split   : 1
% 3.57/1.60  #Chain   : 0
% 3.57/1.60  #Close   : 0
% 3.57/1.60  
% 3.57/1.60  Ordering : KBO
% 3.57/1.60  
% 3.57/1.60  Simplification rules
% 3.57/1.60  ----------------------
% 3.57/1.60  #Subsume      : 55
% 3.57/1.60  #Demod        : 126
% 3.57/1.60  #Tautology    : 165
% 3.57/1.60  #SimpNegUnit  : 1
% 3.57/1.60  #BackRed      : 7
% 3.57/1.60  
% 3.57/1.60  #Partial instantiations: 0
% 3.57/1.60  #Strategies tried      : 1
% 3.57/1.60  
% 3.57/1.60  Timing (in seconds)
% 3.57/1.60  ----------------------
% 3.57/1.60  Preprocessing        : 0.30
% 3.57/1.60  Parsing              : 0.15
% 3.57/1.60  CNF conversion       : 0.02
% 3.57/1.60  Main loop            : 0.53
% 3.57/1.60  Inferencing          : 0.20
% 3.57/1.60  Reduction            : 0.16
% 3.57/1.60  Demodulation         : 0.11
% 3.57/1.60  BG Simplification    : 0.03
% 3.57/1.60  Subsumption          : 0.11
% 3.57/1.60  Abstraction          : 0.02
% 3.57/1.60  MUC search           : 0.00
% 3.57/1.60  Cooper               : 0.00
% 3.57/1.60  Total                : 0.86
% 3.57/1.60  Index Insertion      : 0.00
% 3.57/1.60  Index Deletion       : 0.00
% 3.57/1.60  Index Matching       : 0.00
% 3.57/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
