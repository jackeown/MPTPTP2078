%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:20 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   63 (  88 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 135 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_85,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_127,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [C_36] :
      ( ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
      | ~ r2_hidden(C_36,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_127])).

tff(c_151,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_586,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k3_subset_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_590,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_586])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,(
    ! [A_37,B_38] :
      ( ~ r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_152,plain,(
    ! [A_39,B_40] : k3_xboole_0(k4_xboole_0(A_39,B_40),B_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_146])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_157,plain,(
    ! [A_39,B_40,C_7] :
      ( ~ r1_xboole_0(k4_xboole_0(A_39,B_40),B_40)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_6])).

tff(c_179,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_157])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_68,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_202,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_xboole_0(A_44,B_45)
      | ~ r1_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_214,plain,(
    ! [A_47] :
      ( r1_xboole_0(A_47,'#skF_4')
      | ~ r1_xboole_0(A_47,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_202])).

tff(c_220,plain,(
    ! [A_48] : r1_xboole_0(k4_xboole_0(A_48,'#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_214])).

tff(c_144,plain,(
    ! [A_34,B_35] :
      ( ~ r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_241,plain,(
    ! [A_49] : k3_xboole_0(k4_xboole_0(A_49,'#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_220,c_144])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_252,plain,(
    ! [A_49] : k3_xboole_0('#skF_4',k4_xboole_0(A_49,'#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_2])).

tff(c_425,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),k3_xboole_0(A_67,B_68))
      | r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_431,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_1'('#skF_4',k4_xboole_0(A_49,'#skF_5')),k1_xboole_0)
      | r1_xboole_0('#skF_4',k4_xboole_0(A_49,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_425])).

tff(c_454,plain,(
    ! [A_49] : r1_xboole_0('#skF_4',k4_xboole_0(A_49,'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_431])).

tff(c_593,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_454])).

tff(c_615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_593])).

tff(c_618,plain,(
    ! [C_80] : ~ r2_hidden(C_80,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_622,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_618])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  
% 2.78/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.78/1.40  
% 2.78/1.40  %Foreground sorts:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Background operators:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Foreground operators:
% 2.78/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.78/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.78/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.40  
% 2.78/1.41  tff(f_90, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.78/1.41  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.78/1.41  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.78/1.41  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.78/1.41  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.78/1.41  tff(f_77, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.78/1.41  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.78/1.41  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.78/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.78/1.41  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.78/1.41  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.78/1.41  tff(c_28, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.78/1.41  tff(c_85, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.41  tff(c_92, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_28, c_85])).
% 2.78/1.41  tff(c_127, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.41  tff(c_130, plain, (![C_36]: (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r2_hidden(C_36, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_127])).
% 2.78/1.41  tff(c_151, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_130])).
% 2.78/1.41  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.78/1.41  tff(c_586, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k3_subset_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.78/1.41  tff(c_590, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_586])).
% 2.78/1.41  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.78/1.41  tff(c_146, plain, (![A_37, B_38]: (~r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_127])).
% 2.78/1.41  tff(c_152, plain, (![A_39, B_40]: (k3_xboole_0(k4_xboole_0(A_39, B_40), B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_146])).
% 2.78/1.41  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.41  tff(c_157, plain, (![A_39, B_40, C_7]: (~r1_xboole_0(k4_xboole_0(A_39, B_40), B_40) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_152, c_6])).
% 2.78/1.41  tff(c_179, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_157])).
% 2.78/1.41  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.78/1.41  tff(c_68, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.78/1.41  tff(c_76, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_30, c_68])).
% 2.78/1.41  tff(c_202, plain, (![A_44, B_45, C_46]: (r1_xboole_0(A_44, B_45) | ~r1_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.41  tff(c_214, plain, (![A_47]: (r1_xboole_0(A_47, '#skF_4') | ~r1_xboole_0(A_47, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_202])).
% 2.78/1.41  tff(c_220, plain, (![A_48]: (r1_xboole_0(k4_xboole_0(A_48, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_214])).
% 2.78/1.41  tff(c_144, plain, (![A_34, B_35]: (~r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_127])).
% 2.78/1.41  tff(c_241, plain, (![A_49]: (k3_xboole_0(k4_xboole_0(A_49, '#skF_5'), '#skF_4')=k1_xboole_0)), inference(resolution, [status(thm)], [c_220, c_144])).
% 2.78/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.41  tff(c_252, plain, (![A_49]: (k3_xboole_0('#skF_4', k4_xboole_0(A_49, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_241, c_2])).
% 2.78/1.41  tff(c_425, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), k3_xboole_0(A_67, B_68)) | r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.41  tff(c_431, plain, (![A_49]: (r2_hidden('#skF_1'('#skF_4', k4_xboole_0(A_49, '#skF_5')), k1_xboole_0) | r1_xboole_0('#skF_4', k4_xboole_0(A_49, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_252, c_425])).
% 2.78/1.41  tff(c_454, plain, (![A_49]: (r1_xboole_0('#skF_4', k4_xboole_0(A_49, '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_179, c_431])).
% 2.78/1.41  tff(c_593, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_590, c_454])).
% 2.78/1.41  tff(c_615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_593])).
% 2.78/1.41  tff(c_618, plain, (![C_80]: (~r2_hidden(C_80, '#skF_4'))), inference(splitRight, [status(thm)], [c_130])).
% 2.78/1.41  tff(c_622, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_618])).
% 2.78/1.41  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_622])).
% 2.78/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.41  
% 2.78/1.41  Inference rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Ref     : 0
% 2.78/1.41  #Sup     : 154
% 2.78/1.41  #Fact    : 0
% 2.78/1.41  #Define  : 0
% 2.78/1.41  #Split   : 3
% 2.78/1.41  #Chain   : 0
% 2.78/1.41  #Close   : 0
% 2.78/1.41  
% 2.78/1.41  Ordering : KBO
% 2.78/1.41  
% 2.78/1.41  Simplification rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Subsume      : 9
% 2.78/1.41  #Demod        : 32
% 2.78/1.41  #Tautology    : 66
% 2.78/1.41  #SimpNegUnit  : 8
% 2.78/1.41  #BackRed      : 0
% 2.78/1.41  
% 2.78/1.41  #Partial instantiations: 0
% 2.78/1.41  #Strategies tried      : 1
% 2.78/1.41  
% 2.78/1.41  Timing (in seconds)
% 2.78/1.41  ----------------------
% 2.78/1.41  Preprocessing        : 0.31
% 2.78/1.41  Parsing              : 0.17
% 2.78/1.41  CNF conversion       : 0.02
% 2.78/1.41  Main loop            : 0.32
% 2.78/1.41  Inferencing          : 0.11
% 2.78/1.41  Reduction            : 0.11
% 2.78/1.41  Demodulation         : 0.08
% 2.78/1.41  BG Simplification    : 0.01
% 2.78/1.41  Subsumption          : 0.06
% 2.78/1.41  Abstraction          : 0.01
% 2.78/1.41  MUC search           : 0.00
% 2.78/1.41  Cooper               : 0.00
% 2.78/1.41  Total                : 0.66
% 2.78/1.41  Index Insertion      : 0.00
% 2.78/1.41  Index Deletion       : 0.00
% 2.78/1.41  Index Matching       : 0.00
% 2.78/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
